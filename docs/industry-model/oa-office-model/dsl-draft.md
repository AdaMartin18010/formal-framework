# OA办公模型DSL草案

## 1. 概述

OA办公模型DSL用于统一描述办公自动化系统：文档管理、沟通协作、日历会议、工作流自动化等，支持与SharePoint、Teams、Slack、Jira、Confluence等平台对接。

## 2. 核心语法定义

### 2.1 文档管理

```yaml
document_management:
  repositories:
    - name: "company_docs"
      type: "sharepoint"
      url: "https://company.sharepoint.com/sites/docs"
      permissions:
        - role: "admin"; users: ["admin_group"]
        - role: "editor"; users: ["department_managers"]
        - role: "viewer"; users: ["all_employees"]
      retention_policy:
        default_retention_years: 7
        legal_hold: true
        auto_archive: true
  
  document_types:
    - name: "policy"
      template: "policy_template.docx"
      approval_workflow: "policy_approval"
      version_control: true
      required_fields: ["title", "department", "effective_date", "review_date"]
    - name: "contract"
      template: "contract_template.docx"
      approval_workflow: "contract_approval"
      version_control: true
      required_fields: ["contract_number", "vendor", "start_date", "end_date", "value"]
    - name: "report"
      template: "report_template.pptx"
      approval_workflow: "report_review"
      version_control: true
      required_fields: ["title", "author", "department", "date"]
  
  search_indexing:
    - content_types: ["pdf", "docx", "pptx", "xlsx"]
    - metadata_fields: ["title", "author", "department", "tags", "created_date"]
    - full_text_search: true
    - faceted_search: ["department", "document_type", "date_range"]
```

### 2.2 沟通协作

```yaml
communication_collaboration:
  channels:
    - name: "general"
      type: "public"
      platform: "teams"
      members: ["all_employees"]
      purpose: "Company-wide announcements and discussions"
      moderation: "admin_only"
    - name: "engineering"
      type: "private"
      platform: "slack"
      members: ["engineering_team"]
      purpose: "Engineering team discussions"
      moderation: "team_lead"
    - name: "project_alpha"
      type: "private"
      platform: "teams"
      members: ["project_team"]
      purpose: "Project Alpha discussions"
      moderation: "project_manager"
  
  messaging:
    - platform: "teams"
      features: ["chat", "video_call", "screen_share", "file_sharing"]
      retention_days: 365
      encryption: "end_to_end"
    - platform: "slack"
      features: ["chat", "threads", "integrations", "bots"]
      retention_days: 90
      encryption: "in_transit"
  
  video_conferencing:
    - platform: "teams"
      max_participants: 300
      recording: true
      transcription: true
      breakout_rooms: true
    - platform: "zoom"
      max_participants: 1000
      recording: true
      transcription: false
      breakout_rooms: true
```

### 2.3 日历与会议

```yaml
calendar_meeting:
  calendars:
    - name: "company_calendar"
      type: "public"
      owner: "admin"
      events: ["holidays", "company_events", "maintenance_windows"]
    - name: "meeting_rooms"
      type: "resource"
      rooms: ["conference_room_a", "conference_room_b", "huddle_room_1"]
      booking_policy: "first_come_first_serve"
      max_duration_hours: 4
    - name: "department_calendar"
      type: "shared"
      members: ["department_employees"]
      events: ["team_meetings", "deadlines", "milestones"]
  
  meeting_templates:
    - name: "daily_standup"
      duration_minutes: 15
      participants: ["team_members"]
      agenda_template: "standup_agenda.md"
      recurring: "daily"
      time: "09:00"
    - name: "project_review"
      duration_minutes: 60
      participants: ["project_team", "stakeholders"]
      agenda_template: "project_review_agenda.md"
      recurring: "weekly"
      day: "Friday"
      time: "14:00"
    - name: "client_meeting"
      duration_minutes: 90
      participants: ["account_manager", "technical_lead", "client"]
      agenda_template: "client_meeting_agenda.md"
      recurring: "as_needed"
  
  scheduling:
    - algorithm: "find_optimal_time"
      constraints: ["participant_availability", "room_availability", "timezone"]
      preferences: ["avoid_lunch_hours", "prefer_morning", "max_2_hours"]
    - notifications:
        reminder_minutes: [15, 60, 1440]  # 15min, 1hour, 1day
        channels: ["email", "calendar", "mobile_push"]
```

### 2.4 工作流自动化

```yaml
workflow_automation:
  workflows:
    - name: "expense_approval"
      trigger: "expense_submitted"
      steps:
        - name: "manager_approval"
          role: "direct_manager"
          action: "approve_or_reject"
          timeout_days: 3
          escalation: "skip_to_next"
        - name: "finance_review"
          role: "finance_team"
          action: "review_and_approve"
          timeout_days: 2
          escalation: "notify_admin"
        - name: "payment_processing"
          role: "system"
          action: "process_payment"
          automatic: true
      notifications:
        - step: "manager_approval"
          recipients: ["submitter", "manager"]
          template: "expense_pending_approval"
        - step: "finance_review"
          recipients: ["submitter", "finance_team"]
          template: "expense_under_review"
  
  forms:
    - name: "expense_form"
      fields:
        - name: "expense_type"; type: "dropdown"; required: true
          options: ["travel", "meals", "supplies", "training"]
        - name: "amount"; type: "currency"; required: true
          validation: "min:0, max:10000"
        - name: "description"; type: "text"; required: true
          validation: "max_length:500"
        - name: "receipt"; type: "file"; required: true
          validation: "file_type:pdf,jpg,png, max_size:5MB"
      workflow: "expense_approval"
```

### 2.5 知识管理

```yaml
knowledge_management:
  wikis:
    - name: "company_wiki"
      platform: "confluence"
      spaces:
        - name: "general"
          purpose: "Company policies and procedures"
          permissions: ["all_employees:read", "hr_team:edit"]
        - name: "technical"
          purpose: "Technical documentation"
          permissions: ["engineering_team:edit", "all_employees:read"]
        - name: "projects"
          purpose: "Project documentation"
          permissions: ["project_teams:edit", "stakeholders:read"]
  
  faqs:
    - category: "hr"
      questions:
        - question: "How do I request time off?"
          answer: "Submit a request through the HR portal..."
          tags: ["time_off", "hr", "request"]
        - question: "What is the dress code?"
          answer: "Business casual Monday-Thursday..."
          tags: ["dress_code", "policy", "hr"]
  
  search:
    - engine: "elasticsearch"
      index_sources: ["wiki", "documents", "emails", "chat_history"]
      ranking_factors: ["relevance", "recency", "authority"]
      filters: ["department", "document_type", "date_range"]
```

## 3. 自动化生成示例

```python
# 基于工作流定义自动生成审批流程
def generate_approval_workflow(workflow_config):
    workflow = {
        "name": workflow_config["name"],
        "steps": []
    }
    
    for step in workflow_config["steps"]:
        workflow_step = {
            "name": step["name"],
            "assignee": step["role"],
            "action": step["action"],
            "timeout": step["timeout_days"]
        }
        
        if step.get("automatic"):
            workflow_step["type"] = "system_task"
        else:
            workflow_step["type"] = "user_task"
            workflow_step["notifications"] = generate_notifications(step)
        
        workflow["steps"].append(workflow_step)
    
    return workflow
```

## 4. 验证与测试

```python
class OAOfficeValidator:
    def validate_workflow(self, workflow):
        assert "name" in workflow, "workflow must have name"
        assert "steps" in workflow, "workflow must have steps"
        assert len(workflow["steps"]) > 0, "workflow must have at least one step"
    
    def validate_calendar(self, calendar):
        assert "name" in calendar, "calendar must have name"
        assert "type" in calendar, "calendar must have type"
```

## 5. 总结

本DSL覆盖OA办公领域的核心功能，支持文档管理、沟通协作、日历会议、工作流自动化的自动化配置生成，可与现代办公协作平台无缝集成。
